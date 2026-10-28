import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7180 = true := by
  decide +kernel

theorem tot7180 : totK PA10K2 A10K2.t7180 = [0, 298156594861, 1181858986057, 1739707849187, 1282769525941, 424621155829, 30829329317, 0, 0, 0] := by
  decide +kernel

theorem rows7181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7181 = true := by
  decide +kernel

theorem tot7181 : totK PA10K2 A10K2.t7181 = [0, 466018732676, 1786268731204, 1975449329610, 618841604503, 42744104741, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7182 = true := by
  decide +kernel

theorem tot7182 : totK PA10K2 A10K2.t7182 = [0, 0, 478413169878, 1914152594246, 1823755714526, 421813480439, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows7183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7183 = true := by
  decide +kernel

theorem tot7183 : totK PA10K2 A10K2.t7183 = [0, 454839317077, 1633920776268, 1864540886382, 807351380295, 146837940049, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
