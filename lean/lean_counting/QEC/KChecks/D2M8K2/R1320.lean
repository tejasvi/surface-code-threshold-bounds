import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5280 = true := by
  decide +kernel

theorem tot5280 : totK PD2M8K2 D2M8K2.t5280 = [0, 0, 261504549963, 441674626983, 193431511762, 21382878902, 0, 0] := by
  decide +kernel

theorem rows5281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5281 = true := by
  decide +kernel

theorem tot5281 : totK PD2M8K2 D2M8K2.t5281 = [0, 0, 174794046819, 499372759017, 223729897080, 7968058358, 0, 0] := by
  decide +kernel

theorem rows5282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5282 = true := by
  decide +kernel

theorem tot5282 : totK PD2M8K2 D2M8K2.t5282 = [0, 104023951613, 314356466542, 323011105599, 141839359998, 8209931632, 0, 0] := by
  decide +kernel

theorem rows5283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5283 = true := by
  decide +kernel

theorem tot5283 : totK PD2M8K2 D2M8K2.t5283 = [0, 162611368327, 447885003703, 282859013943, 30173504110, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
