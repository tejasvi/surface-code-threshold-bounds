import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6424 = true := by
  decide +kernel

theorem tot6424 : totK PA10K2 A10K2.t6424 = [376643207835, 1599048759040, 2089430190378, 859816761481, 78829319771, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6425 = true := by
  decide +kernel

theorem tot6425 : totK PA10K2 A10K2.t6425 = [0, 545485262590, 1913882595738, 1846013615676, 483288878108, 31677228370, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6426 = true := by
  decide +kernel

theorem tot6426 : totK PA10K2 A10K2.t6426 = [552281001671, 1910756344574, 1895303385887, 611489708652, 57875494352, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6427 = true := by
  decide +kernel

theorem tot6427 : totK PA10K2 A10K2.t6427 = [330865856800, 1521209393289, 2174609799452, 890712622554, 76142392446, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
