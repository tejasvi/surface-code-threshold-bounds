import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5200 = true := by
  decide +kernel

theorem tot5200 : totK PD2M8K2 D2M8K2.t5200 = [0, 0, 0, 229185118956, 485176309500, 178394777429, 6769157880, 0] := by
  decide +kernel

theorem rows5201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5201 = true := by
  decide +kernel

theorem tot5201 : totK PD2M8K2 D2M8K2.t5201 = [0, 0, 0, 181610363877, 476341389809, 208456718843, 11974190608, 0] := by
  decide +kernel

theorem rows5202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5202 = true := by
  decide +kernel

theorem tot5202 : totK PD2M8K2 D2M8K2.t5202 = [0, 0, 0, 219052384481, 468626014702, 182537790295, 11147507285, 0] := by
  decide +kernel

theorem rows5203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5203 = true := by
  decide +kernel

theorem tot5203 : totK PD2M8K2 D2M8K2.t5203 = [0, 0, 0, 191377601787, 485483380802, 192314657954, 10871000096, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
