import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5236 = true := by
  decide +kernel

theorem tot5236 : totK PA10K2 A10K2.t5236 = [0, 0, 0, 465769320664, 1881394714781, 1860433093934, 436924477601, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5237 = true := by
  decide +kernel

theorem tot5237 : totK PA10K2 A10K2.t5237 = [0, 0, 469339957255, 1672646308883, 1801125189102, 733423361921, 124402031594, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5238 = true := by
  decide +kernel

theorem tot5238 : totK PA10K2 A10K2.t5238 = [0, 0, 109108466041, 926144174418, 2086695869213, 1302496234054, 201293827299, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5239 = true := by
  decide +kernel

theorem tot5239 : totK PA10K2 A10K2.t5239 = [0, 0, 471209682958, 1667808366589, 1874680764341, 629648043516, 51466866980, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
