import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t768 = true := by
  decide +kernel

theorem tot768 : totK PA10K2 A10K2.t768 = [0, 173412559209, 934560915050, 1971291248426, 1418976529771, 245359146737, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t769 = true := by
  decide +kernel

theorem tot769 : totK PA10K2 A10K2.t769 = [0, 468384193772, 1816981363057, 1931569161630, 539835348762, 31614405859, 0, 0, 0, 0] := by
  decide +kernel

theorem rows770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t770 = true := by
  decide +kernel

theorem tot770 : totK PA10K2 A10K2.t770 = [0, 0, 741879925957, 2229283941466, 1477234227703, 167236675897, 0, 0, 0, 0] := by
  decide +kernel

theorem rows771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t771 = true := by
  decide +kernel

theorem tot771 : totK PA10K2 A10K2.t771 = [0, 591472297216, 1903735736994, 1934192702803, 548770454042, 58817353422, 5705019915, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
