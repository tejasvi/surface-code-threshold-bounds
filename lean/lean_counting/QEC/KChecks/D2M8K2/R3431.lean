import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13724 = true := by
  decide +kernel

theorem tot13724 : totK PD2M8K2 D2M8K2.t13724 = [0, 0, 287678095778, 491401045960, 106563604917, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13725 = true := by
  decide +kernel

theorem tot13725 : totK PD2M8K2 D2M8K2.t13725 = [0, 89016638454, 373266756423, 397736630119, 55438129802, 0, 0, 0] := by
  decide +kernel

theorem rows13726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13726 = true := by
  decide +kernel

theorem tot13726 : totK PD2M8K2 D2M8K2.t13726 = [0, 156846216414, 447207205839, 282670104475, 21021526000, 0, 0, 0] := by
  decide +kernel

theorem rows13727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13727 = true := by
  decide +kernel

theorem tot13727 : totK PD2M8K2 D2M8K2.t13727 = [0, 85150114187, 393287495703, 393472505298, 56597852155, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
