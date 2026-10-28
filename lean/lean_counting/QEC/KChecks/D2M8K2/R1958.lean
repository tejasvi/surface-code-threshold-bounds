import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7832 = true := by
  decide +kernel

theorem tot7832 : totK PD2M8K2 D2M8K2.t7832 = [0, 0, 154856210001, 456438754720, 284543248384, 25958715763, 0, 0] := by
  decide +kernel

theorem rows7833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7833 = true := by
  decide +kernel

theorem tot7833 : totK PD2M8K2 D2M8K2.t7833 = [0, 0, 0, 207037811872, 466486284714, 212894498607, 13735775371, 0] := by
  decide +kernel

theorem rows7834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7834 = true := by
  decide +kernel

theorem tot7834 : totK PD2M8K2 D2M8K2.t7834 = [0, 0, 67236046414, 342884052897, 386841950449, 96753939268, 1353333895, 0] := by
  decide +kernel

theorem rows7835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7835 = true := by
  decide +kernel

theorem tot7835 : totK PD2M8K2 D2M8K2.t7835 = [0, 0, 181484076332, 452121980833, 267068135828, 27646366219, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
