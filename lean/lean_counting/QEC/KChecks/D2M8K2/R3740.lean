import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14960 = true := by
  decide +kernel

theorem tot14960 : totK PD2M8K2 D2M8K2.t14960 = [0, 180127341725, 466555128948, 242571540359, 15852968037, 0, 0, 0] := by
  decide +kernel

theorem rows14961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14961 = true := by
  decide +kernel

theorem tot14961 : totK PD2M8K2 D2M8K2.t14961 = [0, 0, 289772365220, 503908879786, 114051136911, 1248762627, 0, 0] := by
  decide +kernel

theorem rows14962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14962 = true := by
  decide +kernel

theorem tot14962 : totK PD2M8K2 D2M8K2.t14962 = [0, 0, 211767050374, 479442353724, 178413157383, 7352468738, 0, 0] := by
  decide +kernel

theorem rows14963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14963 = true := by
  decide +kernel

theorem tot14963 : totK PD2M8K2 D2M8K2.t14963 = [0, 178101248760, 373938923899, 216402335363, 114161923624, 13329350693, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
