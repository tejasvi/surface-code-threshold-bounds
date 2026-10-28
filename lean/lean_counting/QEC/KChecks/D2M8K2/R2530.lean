import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10120 = true := by
  decide +kernel

theorem tot10120 : totK PD2M8K2 D2M8K2.t10120 = [0, 0, 69365834182, 368037353882, 376427352726, 59824372503, 1053411165, 0] := by
  decide +kernel

theorem rows10121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10121 = true := by
  decide +kernel

theorem tot10121 : totK PD2M8K2 D2M8K2.t10121 = [0, 0, 49366429610, 293557110481, 410573684477, 96629577248, 3667207281, 0] := by
  decide +kernel

theorem rows10122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10122 = true := by
  decide +kernel

theorem tot10122 : totK PD2M8K2 D2M8K2.t10122 = [0, 0, 185740540474, 458775580817, 245359935265, 20872377286, 0, 0] := by
  decide +kernel

theorem rows10123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10123 = true := by
  decide +kernel

theorem tot10123 : totK PD2M8K2 D2M8K2.t10123 = [0, 0, 180937872387, 472653942163, 244084185021, 12306796103, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
