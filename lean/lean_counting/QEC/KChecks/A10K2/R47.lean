import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t188 = true := by
  decide +kernel

theorem tot188 : totK PA10K2 A10K2.t188 = [0, 520350426851, 1921396615064, 2070832625738, 579308019611, 22788963204, 0, 0, 0, 0] := by
  decide +kernel

theorem rows189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t189 = true := by
  decide +kernel

theorem tot189 : totK PA10K2 A10K2.t189 = [0, 0, 657109182444, 2153563647282, 1876499147953, 349434971947, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t190 = true := by
  decide +kernel

theorem tot190 : totK PA10K2 A10K2.t190 = [0, 0, 523424680391, 1799339289573, 1950055738563, 685017624605, 55498468803, 0, 0, 0] := by
  decide +kernel

theorem rows191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t191 = true := by
  decide +kernel

theorem tot191 : totK PA10K2 A10K2.t191 = [0, 0, 449191262908, 1772878505002, 1949623912478, 517775313063, 31112697984, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
