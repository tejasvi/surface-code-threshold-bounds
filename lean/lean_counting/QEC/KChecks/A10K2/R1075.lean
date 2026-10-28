import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4300 = true := by
  decide +kernel

theorem tot4300 : totK PA10K2 A10K2.t4300 = [0, 176110335577, 693932614418, 1568733856724, 1767782678438, 628355688984, 41737205306, 0, 0, 0] := by
  decide +kernel

theorem rows4301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4301 = true := by
  decide +kernel

theorem tot4301 : totK PA10K2 A10K2.t4301 = [0, 447196724513, 1769781062188, 2001552223069, 561029989659, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4302 = true := by
  decide +kernel

theorem tot4302 : totK PA10K2 A10K2.t4302 = [0, 173018311605, 1022785213949, 1956145877890, 1392051395492, 349676380128, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4303 = true := by
  decide +kernel

theorem tot4303 : totK PA10K2 A10K2.t4303 = [0, 201767328808, 1021377853467, 1937716814099, 1405112135068, 235420530203, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
