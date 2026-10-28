import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t540 = true := by
  decide +kernel

theorem tot540 : totK PA10K2 A10K2.t540 = [0, 456373900859, 1838279806157, 1904295575355, 443860386547, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t541 = true := by
  decide +kernel

theorem tot541 : totK PA10K2 A10K2.t541 = [482480945578, 1666661908292, 1781579183471, 762577985174, 142784946969, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t542 = true := by
  decide +kernel

theorem tot542 : totK PA10K2 A10K2.t542 = [298064684126, 1545455112440, 2144551030982, 749420438319, 53383554103, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t543 = true := by
  decide +kernel

theorem tot543 : totK PA10K2 A10K2.t543 = [110960779961, 834238673178, 2023935748168, 1472288700061, 248638969737, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
