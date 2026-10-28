import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1916 = true := by
  decide +kernel

theorem tot1916 : totK PD2M8K2 D2M8K2.t1916 = [0, 107956299912, 420003929624, 341725838443, 34395990312, 0, 0, 0] := by
  decide +kernel

theorem rows1917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1917 = true := by
  decide +kernel

theorem tot1917 : totK PD2M8K2 D2M8K2.t1917 = [0, 0, 211209270448, 481539671764, 180760547136, 9583672031, 0, 0] := by
  decide +kernel

theorem rows1918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1918 = true := by
  decide +kernel

theorem tot1918 : totK PD2M8K2 D2M8K2.t1918 = [0, 101506815800, 350910519799, 350270730772, 89592946142, 3460111309, 0, 0] := by
  decide +kernel

theorem rows1919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1919 = true := by
  decide +kernel

theorem tot1919 : totK PD2M8K2 D2M8K2.t1919 = [0, 201295169552, 478742751415, 228424671972, 11735883911, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
