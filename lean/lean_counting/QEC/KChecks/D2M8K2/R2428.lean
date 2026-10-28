import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9712 = true := by
  decide +kernel

theorem tot9712 : totK PD2M8K2 D2M8K2.t9712 = [0, 0, 160260766516, 460748791082, 223584927715, 14625222328, 0, 0] := by
  decide +kernel

theorem rows9713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9713 = true := by
  decide +kernel

theorem tot9713 : totK PD2M8K2 D2M8K2.t9713 = [0, 0, 219315493900, 485907228747, 166461927491, 5186575791, 0, 0] := by
  decide +kernel

theorem rows9714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9714 = true := by
  decide +kernel

theorem tot9714 : totK PD2M8K2 D2M8K2.t9714 = [0, 0, 19348689120, 330254437662, 430855444463, 65939887992, 1200365979, 0] := by
  decide +kernel

theorem rows9715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9715 = true := by
  decide +kernel

theorem tot9715 : totK PD2M8K2 D2M8K2.t9715 = [0, 0, 91626076252, 423459702566, 350747070511, 28997593651, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
