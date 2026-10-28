import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10808 = true := by
  decide +kernel

theorem tot10808 : totK PD2M8K2 D2M8K2.t10808 = [0, 158149307425, 445539207575, 301644828128, 32098608077, 0, 0, 0] := by
  decide +kernel

theorem rows10809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10809 = true := by
  decide +kernel

theorem tot10809 : totK PD2M8K2 D2M8K2.t10809 = [0, 195399766623, 468596805441, 223129773940, 15721908914, 0, 0, 0] := by
  decide +kernel

theorem rows10810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10810 = true := by
  decide +kernel

theorem tot10810 : totK PD2M8K2 D2M8K2.t10810 = [0, 59913483018, 338132848588, 420295532925, 89446265717, 1197396724, 0, 0] := by
  decide +kernel

theorem rows10811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10811 = true := by
  decide +kernel

theorem tot10811 : totK PD2M8K2 D2M8K2.t10811 = [0, 0, 197994853358, 477129488188, 189348451320, 12006692157, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
