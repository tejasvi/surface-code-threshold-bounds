import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1080 = true := by
  decide +kernel

theorem tot1080 : totK PA10K2 A10K2.t1080 = [0, 0, 226020069754, 1229893490847, 2116045835984, 1176449343056, 184987154052, 12696458652, 0, 0] := by
  decide +kernel

theorem rows1081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1081 = true := by
  decide +kernel

theorem tot1081 : totK PA10K2 A10K2.t1081 = [0, 0, 266368802013, 1161158345088, 1868173343528, 1309669493146, 244739230095, 0, 0, 0] := by
  decide +kernel

theorem rows1082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1082 = true := by
  decide +kernel

theorem tot1082 : totK PA10K2 A10K2.t1082 = [0, 0, 315088171453, 1470982819606, 2222446073449, 917048246613, 66838560305, 0, 0, 0] := by
  decide +kernel

theorem rows1083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1083 = true := by
  decide +kernel

theorem tot1083 : totK PA10K2 A10K2.t1083 = [0, 0, 512640208013, 1920145744212, 1986192631493, 546939322942, 23782951814, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
