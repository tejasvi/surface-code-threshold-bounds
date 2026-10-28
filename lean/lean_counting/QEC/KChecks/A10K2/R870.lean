import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3480 = true := by
  decide +kernel

theorem tot3480 : totK PA10K2 A10K2.t3480 = [0, 0, 365936195764, 1265213243497, 1867013210138, 1127735830410, 201312050977, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3481 = true := by
  decide +kernel

theorem tot3481 : totK PA10K2 A10K2.t3481 = [0, 0, 222068787747, 1252990352163, 2091152338470, 1244879501541, 225842377150, 6962742351, 0, 0] := by
  decide +kernel

theorem rows3482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3482 = true := by
  decide +kernel

theorem tot3482 : totK PA10K2 A10K2.t3482 = [0, 0, 0, 605307600560, 2051249946778, 1883214310687, 471647241298, 29739514807, 0, 0] := by
  decide +kernel

theorem rows3483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3483 = true := by
  decide +kernel

theorem tot3483 : totK PA10K2 A10K2.t3483 = [0, 0, 0, 521247221924, 1824886569028, 1854073072781, 508034110653, 32523532663, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
