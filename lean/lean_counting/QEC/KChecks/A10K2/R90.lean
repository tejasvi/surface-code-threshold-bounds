import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t360 = true := by
  decide +kernel

theorem tot360 : totK PA10K2 A10K2.t360 = [0, 262425729187, 1445155578007, 2127913603530, 829447929896, 64592212612, 0, 0, 0, 0] := by
  decide +kernel

theorem rows361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t361 = true := by
  decide +kernel

theorem tot361 : totK PA10K2 A10K2.t361 = [0, 382339736902, 1363287570983, 1839571389203, 1000818744540, 161103514340, 5976421810, 0, 0, 0] := by
  decide +kernel

theorem rows362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t362 = true := by
  decide +kernel

theorem tot362 : totK PA10K2 A10K2.t362 = [0, 431925750211, 1752098735044, 2167937217534, 763538335470, 36346934736, 0, 0, 0, 0] := by
  decide +kernel

theorem rows363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t363 = true := by
  decide +kernel

theorem tot363 : totK PA10K2 A10K2.t363 = [0, 0, 599436198152, 2023608544061, 1957952993651, 463192435168, 13543209714, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
