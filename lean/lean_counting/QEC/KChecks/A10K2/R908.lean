import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3632 = true := by
  decide +kernel

theorem tot3632 : totK PA10K2 A10K2.t3632 = [0, 0, 302082434609, 1511114227523, 2041583713403, 706488477427, 48995886185, 0, 0, 0] := by
  decide +kernel

theorem rows3633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3633 = true := by
  decide +kernel

theorem tot3633 : totK PA10K2 A10K2.t3633 = [0, 202041260899, 521706066817, 796552015213, 1703400232612, 1183576039655, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3634 = true := by
  decide +kernel

theorem tot3634 : totK PA10K2 A10K2.t3634 = [0, 539926926685, 1886379301384, 2008273307870, 565001217174, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3635 = true := by
  decide +kernel

theorem tot3635 : totK PA10K2 A10K2.t3635 = [0, 69280110320, 856199040394, 2100458846926, 1593098586795, 373018902508, 25715051306, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
