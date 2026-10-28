import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14180 = true := by
  decide +kernel

theorem tot14180 : totK PD2M8K2 D2M8K2.t14180 = [0, 35190715666, 234972665343, 459549554680, 152964231368, 5159868635, 0, 0] := by
  decide +kernel

theorem rows14181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14181 = true := by
  decide +kernel

theorem tot14181 : totK PD2M8K2 D2M8K2.t14181 = [0, 170949616633, 437974884935, 280215032972, 30324428842, 0, 0, 0] := by
  decide +kernel

theorem rows14182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14182 = true := by
  decide +kernel

theorem tot14182 : totK PD2M8K2 D2M8K2.t14182 = [0, 121044857238, 447575511610, 319561971060, 33864211839, 0, 0, 0] := by
  decide +kernel

theorem rows14183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14183 = true := by
  decide +kernel

theorem tot14183 : totK PD2M8K2 D2M8K2.t14183 = [0, 0, 218898544636, 495638929495, 166409843536, 5218872685, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
