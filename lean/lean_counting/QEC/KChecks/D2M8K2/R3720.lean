import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14880 = true := by
  decide +kernel

theorem tot14880 : totK PD2M8K2 D2M8K2.t14880 = [0, 211199385206, 494915753549, 195450586501, 6285456587, 0, 0, 0] := by
  decide +kernel

theorem rows14881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14881 = true := by
  decide +kernel

theorem tot14881 : totK PD2M8K2 D2M8K2.t14881 = [173020644527, 376308393586, 246634824369, 100504602581, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows14882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14882 = true := by
  decide +kernel

theorem tot14882 : totK PD2M8K2 D2M8K2.t14882 = [159108482699, 439049057065, 282154742134, 30162361187, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14883 = true := by
  decide +kernel

theorem tot14883 : totK PD2M8K2 D2M8K2.t14883 = [89894498859, 378110141032, 363210367939, 62672364972, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
