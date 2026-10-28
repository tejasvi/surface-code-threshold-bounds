import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1988 = true := by
  decide +kernel

theorem tot1988 : totK PD2M8K2 D2M8K2.t1988 = [0, 34693629254, 321643210817, 445841773674, 100861218265, 1267860612, 0, 0] := by
  decide +kernel

theorem rows1989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1989 = true := by
  decide +kernel

theorem tot1989 : totK PD2M8K2 D2M8K2.t1989 = [0, 0, 217922569547, 493243002740, 171880378712, 5128268972, 0, 0] := by
  decide +kernel

theorem rows1990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1990 = true := by
  decide +kernel

theorem tot1990 : totK PD2M8K2 D2M8K2.t1990 = [0, 0, 161032616197, 429987079727, 296129153354, 33973256189, 0, 0] := by
  decide +kernel

theorem rows1991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1991 = true := by
  decide +kernel

theorem tot1991 : totK PD2M8K2 D2M8K2.t1991 = [0, 0, 192652725664, 484015562576, 222112501157, 10919977507, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
