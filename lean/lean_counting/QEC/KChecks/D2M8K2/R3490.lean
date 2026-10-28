import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13960 = true := by
  decide +kernel

theorem tot13960 : totK PD2M8K2 D2M8K2.t13960 = [0, 0, 202303687247, 469307987140, 182333000008, 8706415949, 0, 0] := by
  decide +kernel

theorem rows13961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13961 = true := by
  decide +kernel

theorem tot13961 : totK PD2M8K2 D2M8K2.t13961 = [0, 156490729458, 440550900798, 289630723646, 38804153234, 0, 0, 0] := by
  decide +kernel

theorem rows13962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13962 = true := by
  decide +kernel

theorem tot13962 : totK PD2M8K2 D2M8K2.t13962 = [0, 176318571452, 458536914613, 245033472960, 15331783090, 0, 0, 0] := by
  decide +kernel

theorem rows13963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13963 = true := by
  decide +kernel

theorem tot13963 : totK PD2M8K2 D2M8K2.t13963 = [0, 87526446010, 351482881256, 384276439335, 70831001210, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
