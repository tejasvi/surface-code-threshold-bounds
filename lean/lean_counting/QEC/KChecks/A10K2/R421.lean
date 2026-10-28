import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1684 = true := by
  decide +kernel

theorem tot1684 : totK PA10K2 A10K2.t1684 = [0, 0, 282936105235, 1170498536347, 1868823531810, 1175844357213, 233565585866, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1685 = true := by
  decide +kernel

theorem tot1685 : totK PA10K2 A10K2.t1685 = [0, 0, 217158502480, 1147484966277, 2074191366359, 1378225055032, 243781638697, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1686 = true := by
  decide +kernel

theorem tot1686 : totK PA10K2 A10K2.t1686 = [0, 0, 470396678568, 1654216420747, 1938677882354, 739792587965, 62866079564, 0, 0, 0] := by
  decide +kernel

theorem rows1687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1687 = true := by
  decide +kernel

theorem tot1687 : totK PA10K2 A10K2.t1687 = [0, 0, 292971234607, 1525223886142, 2201967746815, 846643297120, 52395316567, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
