import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6536 = true := by
  decide +kernel

theorem tot6536 : totK PA10K2 A10K2.t6536 = [0, 0, 307530512419, 1259770309416, 1914968649670, 1070997676367, 141970479737, 5460492893, 0, 0] := by
  decide +kernel

theorem rows6537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6537 = true := by
  decide +kernel

theorem tot6537 : totK PA10K2 A10K2.t6537 = [0, 0, 485154492967, 1848626714002, 1985144253085, 514407017704, 19117496088, 0, 0, 0] := by
  decide +kernel

theorem rows6538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6538 = true := by
  decide +kernel

theorem tot6538 : totK PA10K2 A10K2.t6538 = [0, 0, 0, 615859180538, 2029472801979, 1699735988453, 400381765332, 25734533292, 0, 0] := by
  decide +kernel

theorem rows6539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6539 = true := by
  decide +kernel

theorem tot6539 : totK PA10K2 A10K2.t6539 = [0, 0, 384514750815, 1355820686738, 1745421345285, 1075688132524, 198045764288, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
