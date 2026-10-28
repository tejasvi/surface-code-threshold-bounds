import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7056 = true := by
  decide +kernel

theorem tot7056 : totK PD2M8K2 D2M8K2.t7056 = [0, 0, 211536582155, 485951545393, 180886486382, 9587713104, 0, 0] := by
  decide +kernel

theorem rows7057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7057 = true := by
  decide +kernel

theorem tot7057 : totK PD2M8K2 D2M8K2.t7057 = [0, 87978670910, 315275423157, 383119534365, 100056813709, 3462014130, 0, 0] := by
  decide +kernel

theorem rows7058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7058 = true := by
  decide +kernel

theorem tot7058 : totK PD2M8K2 D2M8K2.t7058 = [0, 169461544141, 459989571179, 245778995887, 15968732945, 0, 0, 0] := by
  decide +kernel

theorem rows7059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7059 = true := by
  decide +kernel

theorem tot7059 : totK PD2M8K2 D2M8K2.t7059 = [0, 138705490129, 441087595313, 283341884915, 20074333972, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
