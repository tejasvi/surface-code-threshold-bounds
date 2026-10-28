import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1852 = true := by
  decide +kernel

theorem tot1852 : totK PD2M8K2 D2M8K2.t1852 = [0, 0, 286523601610, 506711542661, 99095618979, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1853 = true := by
  decide +kernel

theorem tot1853 : totK PD2M8K2 D2M8K2.t1853 = [0, 85045554163, 325915805022, 360198872800, 103900882472, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1854 = true := by
  decide +kernel

theorem tot1854 : totK PD2M8K2 D2M8K2.t1854 = [0, 176146235289, 450324207003, 263714687094, 27097405683, 0, 0, 0] := by
  decide +kernel

theorem rows1855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1855 = true := by
  decide +kernel

theorem tot1855 : totK PD2M8K2 D2M8K2.t1855 = [0, 159635071355, 447350813720, 276879597835, 21654833975, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
