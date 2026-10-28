import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6800 = true := by
  decide +kernel

theorem tot6800 : totK PD2M8K2 D2M8K2.t6800 = [40738718386, 344883845621, 458858518060, 61608400452, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6801 = true := by
  decide +kernel

theorem tot6801 : totK PD2M8K2 D2M8K2.t6801 = [166860428047, 444280192969, 283316770029, 30455970377, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6802 = true := by
  decide +kernel

theorem tot6802 : totK PD2M8K2 D2M8K2.t6802 = [204601796918, 493455723684, 201706279542, 9458558394, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6803 = true := by
  decide +kernel

theorem tot6803 : totK PD2M8K2 D2M8K2.t6803 = [0, 243081006437, 452924329901, 196181759179, 21382878902, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
