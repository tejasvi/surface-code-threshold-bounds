import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1780 = true := by
  decide +kernel

theorem tot1780 : totK PA10K2 A10K2.t1780 = [0, 0, 481114945113, 1634904023857, 1766004551922, 812756078303, 147801874788, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1781 = true := by
  decide +kernel

theorem tot1781 : totK PA10K2 A10K2.t1781 = [0, 0, 298064684126, 1557913770454, 2132378123823, 745959974690, 53383554103, 0, 0, 0] := by
  decide +kernel

theorem rows1782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1782 = true := by
  decide +kernel

theorem tot1782 : totK PA10K2 A10K2.t1782 = [0, 0, 110960779961, 821462686431, 2064910432359, 1475477322818, 248638969737, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1783 = true := by
  decide +kernel

theorem tot1783 : totK PA10K2 A10K2.t1783 = [0, 0, 157101129727, 1041287400940, 1982984075386, 1391080657077, 277262582669, 20589542419, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
