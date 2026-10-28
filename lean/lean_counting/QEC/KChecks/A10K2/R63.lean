import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t252 = true := by
  decide +kernel

theorem tot252 : totK PA10K2 A10K2.t252 = [0, 477482834340, 1764690129001, 2059271250423, 778963985596, 67351211821, 0, 0, 0, 0] := by
  decide +kernel

theorem rows253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t253 = true := by
  decide +kernel

theorem tot253 : totK PA10K2 A10K2.t253 = [0, 110568251524, 868357841713, 2179758722707, 1647948215431, 285441916726, 7380853412, 0, 0, 0] := by
  decide +kernel

theorem rows254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t254 = true := by
  decide +kernel

theorem tot254 : totK PA10K2 A10K2.t254 = [0, 490139521757, 1834814489499, 2007896509427, 582415849522, 36270210307, 0, 0, 0, 0] := by
  decide +kernel

theorem rows255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t255 = true := by
  decide +kernel

theorem tot255 : totK PA10K2 A10K2.t255 = [0, 218977231605, 1357982672791, 2213872849828, 1118598733324, 115926629975, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
