import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12464 = true := by
  decide +kernel

theorem tot12464 : totK PD2M8K2 D2M8K2.t12464 = [0, 0, 178707584483, 464833983654, 226011973592, 16702988424, 0, 0] := by
  decide +kernel

theorem rows12465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12465 = true := by
  decide +kernel

theorem tot12465 : totK PD2M8K2 D2M8K2.t12465 = [0, 0, 0, 311066463174, 454277877841, 84684728902, 1095107716, 0] := by
  decide +kernel

theorem rows12466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12466 = true := by
  decide +kernel

theorem tot12466 : totK PD2M8K2 D2M8K2.t12466 = [0, 92342479873, 134931756560, 203372582983, 345751447187, 106002319956, 3882006667, 0] := by
  decide +kernel

theorem rows12467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12467 = true := by
  decide +kernel

theorem tot12467 : totK PD2M8K2 D2M8K2.t12467 = [0, 175504638366, 482218376830, 237396596558, 11038245751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
