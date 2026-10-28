import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t272 = true := by
  decide +kernel

theorem tot272 : totK PD2M8K2 D2M8K2.t272 = [0, 184533125012, 473367620251, 224658175563, 13551806682, 0, 0, 0] := by
  decide +kernel

theorem rows273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t273 = true := by
  decide +kernel

theorem tot273 : totK PD2M8K2 D2M8K2.t273 = [0, 0, 288988375815, 507914263165, 103414861984, 1129969115, 0, 0] := by
  decide +kernel

theorem rows274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t274 = true := by
  decide +kernel

theorem tot274 : totK PD2M8K2 D2M8K2.t274 = [0, 84995303257, 301042312860, 397860639742, 106819991577, 4008488258, 0, 0] := by
  decide +kernel

theorem rows275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t275 = true := by
  decide +kernel

theorem tot275 : totK PD2M8K2 D2M8K2.t275 = [0, 170414062197, 470000401279, 249581596695, 21001213374, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
