import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13160 = true := by
  decide +kernel

theorem tot13160 : totK PD2M8K2 D2M8K2.t13160 = [0, 68965578832, 279716578988, 364075290375, 176412084984, 21154790189, 0, 0] := by
  decide +kernel

theorem rows13161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13161 = true := by
  decide +kernel

theorem tot13161 : totK PD2M8K2 D2M8K2.t13161 = [0, 0, 208587909053, 482348369930, 205385894706, 7994456143, 0, 0] := by
  decide +kernel

theorem rows13162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13162 = true := by
  decide +kernel

theorem tot13162 : totK PD2M8K2 D2M8K2.t13162 = [0, 80975586946, 250239925701, 373126118456, 177223810849, 6825134885, 0, 0] := by
  decide +kernel

theorem rows13163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13163 = true := by
  decide +kernel

theorem tot13163 : totK PD2M8K2 D2M8K2.t13163 = [0, 173863303949, 476334212924, 250468159641, 16280558213, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
