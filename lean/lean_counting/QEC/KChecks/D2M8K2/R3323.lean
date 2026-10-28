import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13292 = true := by
  decide +kernel

theorem tot13292 : totK PD2M8K2 D2M8K2.t13292 = [0, 0, 185349310117, 474105273711, 231052890291, 9401650850, 0, 0] := by
  decide +kernel

theorem rows13293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13293 = true := by
  decide +kernel

theorem tot13293 : totK PD2M8K2 D2M8K2.t13293 = [0, 157065200967, 374731384823, 264391484218, 98328073235, 5424717144, 0, 0] := by
  decide +kernel

theorem rows13294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13294 = true := by
  decide +kernel

theorem tot13294 : totK PD2M8K2 D2M8K2.t13294 = [0, 166232679222, 442054566976, 284283341785, 30179797769, 0, 0, 0] := by
  decide +kernel

theorem rows13295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13295 = true := by
  decide +kernel

theorem tot13295 : totK PD2M8K2 D2M8K2.t13295 = [0, 116438717738, 431551368353, 318512780129, 25581530397, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
