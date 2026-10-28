import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16256 = true := by
  decide +kernel

theorem tot16256 : totK PD2M8K2 D2M8K2.t16256 = [0, 0, 0, 192239517653, 499813065388, 186587450507, 5342990109, 0] := by
  decide +kernel

theorem rows16257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16257 = true := by
  decide +kernel

theorem tot16257 : totK PD2M8K2 D2M8K2.t16257 = [0, 0, 0, 168545847836, 471631033045, 207970387885, 9951903173, 0] := by
  decide +kernel

theorem rows16258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16258 = true := by
  decide +kernel

theorem tot16258 : totK PD2M8K2 D2M8K2.t16258 = [0, 0, 0, 0, 290297755943, 459326859955, 90747839805, 1369150432] := by
  decide +kernel

theorem rows16259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16259 = true := by
  decide +kernel

theorem tot16259 : totK PD2M8K2 D2M8K2.t16259 = [0, 0, 0, 148290364214, 446707763003, 261719299539, 17486047897, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
