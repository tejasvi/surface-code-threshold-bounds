import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9592 = true := by
  decide +kernel

theorem tot9592 : totK PD2M8K2 D2M8K2.t9592 = [177997545107, 459031734107, 267414337341, 27673538634, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9593 = true := by
  decide +kernel

theorem tot9593 : totK PD2M8K2 D2M8K2.t9593 = [182497872290, 470416713574, 250085615401, 15068350778, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9594 = true := by
  decide +kernel

theorem tot9594 : totK PD2M8K2 D2M8K2.t9594 = [0, 275408119331, 506126226118, 122830947635, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows9595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9595 = true := by
  decide +kernel

theorem tot9595 : totK PD2M8K2 D2M8K2.t9595 = [0, 185293791996, 485270880610, 204744004703, 8669917095, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
