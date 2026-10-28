import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14520 = true := by
  decide +kernel

theorem tot14520 : totK PD2M8K2 D2M8K2.t14520 = [0, 160967727169, 443614998811, 298837421513, 31175922257, 0, 0, 0] := by
  decide +kernel

theorem rows14521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14521 = true := by
  decide +kernel

theorem tot14521 : totK PD2M8K2 D2M8K2.t14521 = [0, 173553959673, 475888404360, 232146348652, 12431188009, 0, 0, 0] := by
  decide +kernel

theorem rows14522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14522 = true := by
  decide +kernel

theorem tot14522 : totK PD2M8K2 D2M8K2.t14522 = [0, 193704307185, 456502347686, 231542070219, 15671754440, 0, 0, 0] := by
  decide +kernel

theorem rows14523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14523 = true := by
  decide +kernel

theorem tot14523 : totK PD2M8K2 D2M8K2.t14523 = [0, 162915979460, 452070389251, 279867273008, 27214788375, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
