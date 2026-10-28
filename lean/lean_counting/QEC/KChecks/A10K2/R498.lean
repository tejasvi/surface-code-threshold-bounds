import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1992 = true := by
  decide +kernel

theorem tot1992 : totK PA10K2 A10K2.t1992 = [0, 0, 478610618287, 1698507984036, 1910337981602, 770955307486, 75989515541, 0, 0, 0] := by
  decide +kernel

theorem rows1993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1993 = true := by
  decide +kernel

theorem tot1993 : totK PA10K2 A10K2.t1993 = [0, 0, 291093484992, 1458988729434, 2146419367908, 834718889922, 65300796175, 0, 0, 0] := by
  decide +kernel

theorem rows1994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1994 = true := by
  decide +kernel

theorem tot1994 : totK PA10K2 A10K2.t1994 = [0, 0, 536325474129, 1899829828245, 2041807930659, 590454353772, 37396946132, 0, 0, 0] := by
  decide +kernel

theorem rows1995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1995 = true := by
  decide +kernel

theorem tot1995 : totK PA10K2 A10K2.t1995 = [0, 0, 0, 756574150039, 2230131481587, 1721517081282, 307433735571, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
