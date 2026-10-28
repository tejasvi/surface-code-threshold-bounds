import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3184 = true := by
  decide +kernel

theorem tot3184 : totK PA10K2 A10K2.t3184 = [0, 0, 609641037450, 2084921651019, 1947446513993, 425006631886, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows3185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3185 = true := by
  decide +kernel

theorem tot3185 : totK PA10K2 A10K2.t3185 = [0, 0, 320437926777, 1530978889319, 2123491916288, 843665805673, 73533260548, 0, 0, 0] := by
  decide +kernel

theorem rows3186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3186 = true := by
  decide +kernel

theorem tot3186 : totK PA10K2 A10K2.t3186 = [0, 0, 552523461095, 1950675089137, 1937370451462, 451942867449, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows3187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3187 = true := by
  decide +kernel

theorem tot3187 : totK PA10K2 A10K2.t3187 = [0, 0, 0, 685735643531, 1998276089809, 1619608804775, 391413943146, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
