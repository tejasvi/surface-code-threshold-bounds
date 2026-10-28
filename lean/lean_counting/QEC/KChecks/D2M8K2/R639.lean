import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2556 = true := by
  decide +kernel

theorem tot2556 : totK PD2M8K2 D2M8K2.t2556 = [75646282140, 246298333128, 380250622942, 184660676903, 8210597527, 0, 0, 0] := by
  decide +kernel

theorem rows2557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2557 = true := by
  decide +kernel

theorem tot2557 : totK PD2M8K2 D2M8K2.t2557 = [180245559322, 461826909141, 250463827330, 23259966184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2558 = true := by
  decide +kernel

theorem tot2558 : totK PD2M8K2 D2M8K2.t2558 = [156729864509, 459077611341, 266155964592, 16062896676, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2559 = true := by
  decide +kernel

theorem tot2559 : totK PD2M8K2 D2M8K2.t2559 = [0, 264521986269, 502969517917, 117816843818, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
