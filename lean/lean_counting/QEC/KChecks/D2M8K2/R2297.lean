import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9188 = true := by
  decide +kernel

theorem tot9188 : totK PD2M8K2 D2M8K2.t9188 = [123837241364, 312719698881, 319758856623, 146606343861, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows9189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9189 = true := by
  decide +kernel

theorem tot9189 : totK PD2M8K2 D2M8K2.t9189 = [159806959770, 431329289222, 279312577441, 30484327524, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9190 = true := by
  decide +kernel

theorem tot9190 : totK PD2M8K2 D2M8K2.t9190 = [100207512347, 393246305559, 338728209595, 64360076440, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows9191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9191 = true := by
  decide +kernel

theorem tot9191 : totK PD2M8K2 D2M8K2.t9191 = [0, 243061244454, 486732368937, 149235340978, 8417083954, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
