import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5032 = true := by
  decide +kernel

theorem tot5032 : totK PA10K2 A10K2.t5032 = [0, 0, 627504632720, 1980404672954, 1726224696609, 371009473684, 11866545492, 0, 0, 0] := by
  decide +kernel

theorem rows5033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5033 = true := by
  decide +kernel

theorem tot5033 : totK PA10K2 A10K2.t5033 = [0, 0, 437118178716, 1698842650556, 1798369888029, 548385780723, 50109395967, 0, 0, 0] := by
  decide +kernel

theorem rows5034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5034 = true := by
  decide +kernel

theorem tot5034 : totK PA10K2 A10K2.t5034 = [0, 0, 207095805940, 1425003745018, 2141512371250, 769217441992, 58344830985, 0, 0, 0] := by
  decide +kernel

theorem rows5035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5035 = true := by
  decide +kernel

theorem tot5035 : totK PA10K2 A10K2.t5035 = [0, 319364639558, 980123121729, 1097524369449, 1194146714918, 889117660028, 207269719194, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
