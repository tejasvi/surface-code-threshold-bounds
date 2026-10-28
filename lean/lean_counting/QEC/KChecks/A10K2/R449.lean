import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1796 = true := by
  decide +kernel

theorem tot1796 : totK PA10K2 A10K2.t1796 = [0, 0, 0, 450381543286, 1744618592680, 1970883311351, 525086932170, 31987876949, 0, 0] := by
  decide +kernel

theorem rows1797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1797 = true := by
  decide +kernel

theorem tot1797 : totK PA10K2 A10K2.t1797 = [0, 0, 0, 524906977709, 1834437135528, 1875274606432, 455546574478, 32480588830, 0, 0] := by
  decide +kernel

theorem rows1798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1798 = true := by
  decide +kernel

theorem tot1798 : totK PA10K2 A10K2.t1798 = [0, 0, 0, 438698900971, 1828852064212, 1931877513158, 493338655197, 31088438951, 0, 0] := by
  decide +kernel

theorem rows1799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1799 = true := by
  decide +kernel

theorem tot1799 : totK PA10K2 A10K2.t1799 = [0, 0, 0, 570974969950, 1930364274934, 1753802224628, 381688582043, 25533540376, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
