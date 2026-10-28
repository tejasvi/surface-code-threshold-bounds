import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10544 = true := by
  decide +kernel

theorem tot10544 : totK PD2M8K2 D2M8K2.t10544 = [0, 178048372752, 464394632844, 242540830524, 16994710084, 0, 0, 0] := by
  decide +kernel

theorem rows10545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10545 = true := by
  decide +kernel

theorem tot10545 : totK PD2M8K2 D2M8K2.t10545 = [0, 0, 301924148571, 496268962927, 96206954229, 1096156699, 0, 0] := by
  decide +kernel

theorem rows10546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10546 = true := by
  decide +kernel

theorem tot10546 : totK PD2M8K2 D2M8K2.t10546 = [0, 90227004997, 324920422261, 395478753838, 109462958262, 3880716147, 0, 0] := by
  decide +kernel

theorem rows10547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10547 = true := by
  decide +kernel

theorem tot10547 : totK PD2M8K2 D2M8K2.t10547 = [0, 154009893344, 446277610351, 295579035458, 27135027020, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
