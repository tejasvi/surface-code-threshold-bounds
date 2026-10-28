import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2872 = true := by
  decide +kernel

theorem tot2872 : totK PA10K2 A10K2.t2872 = [0, 384418616082, 1361157918618, 1750763200360, 1113536596333, 211989801346, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2873 = true := by
  decide +kernel

theorem tot2873 : totK PA10K2 A10K2.t2873 = [0, 357659149530, 1613500139736, 2081812676636, 689728559704, 47188307610, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2874 = true := by
  decide +kernel

theorem tot2874 : totK PA10K2 A10K2.t2874 = [0, 0, 764945567733, 2163938439001, 1501503245828, 253996617070, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2875 = true := by
  decide +kernel

theorem tot2875 : totK PA10K2 A10K2.t2875 = [0, 0, 457725415596, 1908699561546, 1949871586226, 463591691951, 26116334861, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
