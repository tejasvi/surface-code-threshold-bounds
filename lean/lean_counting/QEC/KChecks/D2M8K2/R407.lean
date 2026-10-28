import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1628 = true := by
  decide +kernel

theorem tot1628 : totK PD2M8K2 D2M8K2.t1628 = [0, 0, 0, 322481981152, 451463632680, 73947971655, 1138244013, 0] := by
  decide +kernel

theorem rows1629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1629 = true := by
  decide +kernel

theorem tot1629 : totK PD2M8K2 D2M8K2.t1629 = [0, 0, 155465867603, 464471472058, 258782939964, 16402501105, 0, 0] := by
  decide +kernel

theorem rows1630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1630 = true := by
  decide +kernel

theorem tot1630 : totK PD2M8K2 D2M8K2.t1630 = [0, 0, 169889011488, 482062931652, 220553582039, 11503842116, 0, 0] := by
  decide +kernel

theorem rows1631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1631 = true := by
  decide +kernel

theorem tot1631 : totK PD2M8K2 D2M8K2.t1631 = [0, 0, 198741813931, 472399890117, 200659749384, 7270944541, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
