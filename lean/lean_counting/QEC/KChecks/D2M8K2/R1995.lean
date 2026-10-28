import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7980 = true := by
  decide +kernel

theorem tot7980 : totK PD2M8K2 D2M8K2.t7980 = [0, 0, 200882943342, 463490767288, 230407577825, 20141038265, 0, 0] := by
  decide +kernel

theorem rows7981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7981 = true := by
  decide +kernel

theorem tot7981 : totK PD2M8K2 D2M8K2.t7981 = [0, 0, 180846176614, 457918227476, 231650636276, 16994558090, 0, 0] := by
  decide +kernel

theorem rows7982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7982 = true := by
  decide +kernel

theorem tot7982 : totK PD2M8K2 D2M8K2.t7982 = [0, 0, 48383029617, 395884970148, 413938839577, 47769780179, 0, 0] := by
  decide +kernel

theorem rows7983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7983 = true := by
  decide +kernel

theorem tot7983 : totK PD2M8K2 D2M8K2.t7983 = [0, 0, 89862837988, 325069191336, 395225910631, 96211880550, 2813333534, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
