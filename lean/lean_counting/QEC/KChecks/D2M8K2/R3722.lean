import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14888 = true := by
  decide +kernel

theorem tot14888 : totK PD2M8K2 D2M8K2.t14888 = [0, 207261653603, 483774121893, 189407522627, 9652233629, 0, 0, 0] := by
  decide +kernel

theorem rows14889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14889 = true := by
  decide +kernel

theorem tot14889 : totK PD2M8K2 D2M8K2.t14889 = [87123270202, 342204861559, 371683122932, 92921483901, 3419660603, 0, 0, 0] := by
  decide +kernel

theorem rows14890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14890 = true := by
  decide +kernel

theorem tot14890 : totK PD2M8K2 D2M8K2.t14890 = [178588180851, 457511594509, 267951623555, 27673538634, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14891 = true := by
  decide +kernel

theorem tot14891 : totK PD2M8K2 D2M8K2.t14891 = [182497872290, 471007349318, 251210602319, 15566149331, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
