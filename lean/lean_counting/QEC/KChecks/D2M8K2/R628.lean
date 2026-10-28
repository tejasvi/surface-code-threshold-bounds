import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2512 = true := by
  decide +kernel

theorem tot2512 : totK PD2M8K2 D2M8K2.t2512 = [0, 179790919623, 454798713497, 261545531010, 25478622528, 0, 0, 0] := by
  decide +kernel

theorem rows2513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2513 = true := by
  decide +kernel

theorem tot2513 : totK PD2M8K2 D2M8K2.t2513 = [71343817081, 229025870528, 370362567176, 214406742827, 17276618756, 0, 0, 0] := by
  decide +kernel

theorem rows2514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2514 = true := by
  decide +kernel

theorem tot2514 : totK PD2M8K2 D2M8K2.t2514 = [168637168782, 480002496757, 230839515731, 10807940679, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2515 = true := by
  decide +kernel

theorem tot2515 : totK PD2M8K2 D2M8K2.t2515 = [83024820476, 336631335642, 392796659289, 85021490756, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
