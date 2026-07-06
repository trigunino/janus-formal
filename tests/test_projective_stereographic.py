import unittest

import numpy as np

from src.janus_lab.projective_stereographic import (
    antipodal_stereographic_image,
    antipodal_stereographic_radius,
    reciprocal_radius_fixed_point,
)


class ProjectiveStereographicTests(unittest.TestCase):
    def test_antipodal_image_inverts_radius(self):
        image = antipodal_stereographic_image([2.0, 0.0])

        np.testing.assert_allclose(image, [-0.5, 0.0])
        self.assertEqual(antipodal_stereographic_radius(2.0), 0.5)

    def test_fixed_point_is_one(self):
        self.assertEqual(reciprocal_radius_fixed_point(), 1.0)


if __name__ == "__main__":
    unittest.main()
