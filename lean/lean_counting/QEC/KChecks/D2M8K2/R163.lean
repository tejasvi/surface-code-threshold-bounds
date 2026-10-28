import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t652 = true := by
  decide +kernel

theorem tot652 : totK PD2M8K2 D2M8K2.t652 = [157239648738, 364122381319, 149747919196, 114990519105, 91087454472, 6818291842, 0, 0] := by
  decide +kernel

theorem rows653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t653 = true := by
  decide +kernel

theorem tot653 : totK PD2M8K2 D2M8K2.t653 = [173982771809, 470262173825, 237053663815, 13624401152, 0, 0, 0, 0] := by
  decide +kernel

theorem rows654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t654 = true := by
  decide +kernel

theorem tot654 : totK PD2M8K2 D2M8K2.t654 = [86524311424, 326742396668, 383029042450, 91194324437, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t655 = true := by
  decide +kernel

theorem tot655 : totK PD2M8K2 D2M8K2.t655 = [19982995165, 327837628131, 502202124822, 64924249402, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
