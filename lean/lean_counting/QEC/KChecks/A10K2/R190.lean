import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t760 = true := by
  decide +kernel

theorem tot760 : totK PA10K2 A10K2.t760 = [0, 452685553172, 1652419548222, 1997018215536, 814419227638, 76163995249, 0, 0, 0, 0] := by
  decide +kernel

theorem rows761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t761 = true := by
  decide +kernel

theorem tot761 : totK PA10K2 A10K2.t761 = [0, 100309593406, 947555805966, 2160432046522, 1517133776477, 263768695964, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t762 = true := by
  decide +kernel

theorem tot762 : totK PA10K2 A10K2.t762 = [0, 489528904646, 1724222778705, 1917207661623, 745787033772, 62279057361, 0, 0, 0, 0] := by
  decide +kernel

theorem rows763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t763 = true := by
  decide +kernel

theorem tot763 : totK PA10K2 A10K2.t763 = [0, 371876299447, 1659227536631, 2154377142965, 742112195831, 30988517146, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
