import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8160 = true := by
  decide +kernel

theorem tot8160 : totK PA10K2 A10K2.t8160 = [0, 0, 0, 0, 0, 940899913186, 2287238237667, 1319620436797, 199528673010, 6725424603] := by
  decide +kernel

theorem rows8161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8161 = true := by
  decide +kernel

theorem tot8161 : totK PA10K2 A10K2.t8161 = [0, 0, 0, 0, 696893510187, 2056998146177, 1584709485057, 399908530630, 31452125142, 0] := by
  decide +kernel

theorem rows8162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8162 = true := by
  decide +kernel

theorem tot8162 : totK PA10K2 A10K2.t8162 = [0, 0, 0, 0, 553264129374, 2038044715460, 2057030006869, 465780956567, 18066489345, 0] := by
  decide +kernel

theorem rows8163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8163 = true := by
  decide +kernel

theorem tot8163 : totK PA10K2 A10K2.t8163 = [0, 0, 0, 310599358184, 1118027408435, 1527196269066, 1305252703667, 535985677314, 50425690648, 0] := by
  decide +kernel

end QECKChecks.A10K2
