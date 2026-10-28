import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4784 = true := by
  decide +kernel

theorem tot4784 : totK PD2M8K2 D2M8K2.t4784 = [0, 0, 180273317021, 466551841879, 232687097250, 16691388709, 0, 0] := by
  decide +kernel

theorem rows4785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4785 = true := by
  decide +kernel

theorem tot4785 : totK PD2M8K2 D2M8K2.t4785 = [0, 0, 0, 306822947706, 455157584228, 86867240737, 1095107716, 0] := by
  decide +kernel

theorem rows4786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4786 = true := by
  decide +kernel

theorem tot4786 : totK PD2M8K2 D2M8K2.t4786 = [0, 87698990320, 154379024082, 203399701997, 327178227733, 104267637556, 3882006667, 0] := by
  decide +kernel

theorem rows4787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4787 = true := by
  decide +kernel

theorem tot4787 : totK PD2M8K2 D2M8K2.t4787 = [0, 168071512843, 465400263996, 249243502090, 12872662192, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
