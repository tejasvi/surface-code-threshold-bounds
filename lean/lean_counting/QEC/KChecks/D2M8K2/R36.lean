import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t144 = true := by
  decide +kernel

theorem tot144 : totK PD2M8K2 D2M8K2.t144 = [114435939574, 342993255690, 319463558375, 120323330129, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t145 = true := by
  decide +kernel

theorem tot145 : totK PD2M8K2 D2M8K2.t145 = [168959998704, 445334375815, 264294598573, 28497656562, 0, 0, 0, 0] := by
  decide +kernel

theorem rows146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t146 = true := by
  decide +kernel

theorem tot146 : totK PD2M8K2 D2M8K2.t146 = [125706966731, 432648381777, 316403743128, 27763635165, 0, 0, 0, 0] := by
  decide +kernel

theorem rows147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t147 = true := by
  decide +kernel

theorem tot147 : totK PD2M8K2 D2M8K2.t147 = [0, 204611627908, 488323988183, 181997114029, 9583672031, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
