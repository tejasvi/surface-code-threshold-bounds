import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5776 = true := by
  decide +kernel

theorem tot5776 : totK PD2M8K2 D2M8K2.t5776 = [0, 0, 256469653582, 495800774628, 137531432203, 3633193399, 0, 0] := by
  decide +kernel

theorem rows5777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5777 = true := by
  decide +kernel

theorem tot5777 : totK PD2M8K2 D2M8K2.t5777 = [94445126902, 166666727072, 131301211941, 305778319119, 189308161885, 17014456371, 0, 0] := by
  decide +kernel

theorem rows5778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5778 = true := by
  decide +kernel

theorem tot5778 : totK PD2M8K2 D2M8K2.t5778 = [177241867645, 440742732659, 273634821253, 30321150294, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5779 = true := by
  decide +kernel

theorem tot5779 : totK PD2M8K2 D2M8K2.t5779 = [177742938662, 476941153272, 247501217470, 12638521189, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
