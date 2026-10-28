import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1892 = true := by
  decide +kernel

theorem tot1892 : totK PD2M8K2 D2M8K2.t1892 = [0, 0, 326411416249, 517590782617, 72533134849, 0, 0, 0] := by
  decide +kernel

theorem rows1893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1893 = true := by
  decide +kernel

theorem tot1893 : totK PD2M8K2 D2M8K2.t1893 = [0, 0, 175531830492, 491598154152, 208753783497, 6406394852, 0, 0] := by
  decide +kernel

theorem rows1894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1894 = true := by
  decide +kernel

theorem tot1894 : totK PD2M8K2 D2M8K2.t1894 = [0, 0, 164924219687, 453471148631, 229370519246, 16820461111, 0, 0] := by
  decide +kernel

theorem rows1895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1895 = true := by
  decide +kernel

theorem tot1895 : totK PD2M8K2 D2M8K2.t1895 = [0, 0, 67615601996, 347974237829, 370162965715, 65392522394, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
