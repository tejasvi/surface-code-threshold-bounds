import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10924 = true := by
  decide +kernel

theorem tot10924 : totK PD2M8K2 D2M8K2.t10924 = [0, 0, 200421498041, 476200450890, 189516676628, 5098257138, 0, 0] := by
  decide +kernel

theorem rows10925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10925 = true := by
  decide +kernel

theorem tot10925 : totK PD2M8K2 D2M8K2.t10925 = [0, 0, 37595298038, 317108879933, 434956522062, 82331711687, 1310285577, 0] := by
  decide +kernel

theorem rows10926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10926 = true := by
  decide +kernel

theorem tot10926 : totK PD2M8K2 D2M8K2.t10926 = [0, 0, 85117649633, 372315693570, 401419126530, 39806112499, 0, 0] := by
  decide +kernel

theorem rows10927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10927 = true := by
  decide +kernel

theorem tot10927 : totK PD2M8K2 D2M8K2.t10927 = [0, 0, 160869836277, 442767212567, 275205474936, 26922937030, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
