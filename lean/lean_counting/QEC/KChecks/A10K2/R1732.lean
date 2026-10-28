import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6928 = true := by
  decide +kernel

theorem tot6928 : totK PA10K2 A10K2.t6928 = [0, 0, 275973632717, 1213758321449, 1906694302426, 1086882613288, 181691738471, 5460492893, 0, 0] := by
  decide +kernel

theorem rows6929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6929 = true := by
  decide +kernel

theorem tot6929 : totK PA10K2 A10K2.t6929 = [0, 0, 282722822571, 1539119966670, 2201570063967, 701451261740, 38229764397, 0, 0, 0] := by
  decide +kernel

theorem rows6930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6930 = true := by
  decide +kernel

theorem tot6930 : totK PA10K2 A10K2.t6930 = [0, 0, 307133734239, 1215434717443, 1865962304726, 1111433321178, 189349518109, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6931 = true := by
  decide +kernel

theorem tot6931 : totK PA10K2 A10K2.t6931 = [0, 0, 485970986556, 1837711192376, 1981213087340, 583131112762, 24104979924, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
