import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4316 = true := by
  decide +kernel

theorem tot4316 : totK PA10K2 A10K2.t4316 = [0, 360323831806, 1496005981892, 2107818498547, 1039179549502, 109160029562, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4317 = true := by
  decide +kernel

theorem tot4317 : totK PA10K2 A10K2.t4317 = [0, 529385373493, 1934325798471, 2025316406553, 567117162458, 37518967325, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4318 = true := by
  decide +kernel

theorem tot4318 : totK PA10K2 A10K2.t4318 = [0, 100137355278, 923013178380, 2138907685016, 1587754218635, 275031434699, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4319 = true := by
  decide +kernel

theorem tot4319 : totK PA10K2 A10K2.t4319 = [0, 0, 508176788704, 1864869667561, 2061633048652, 598611240314, 18547707510, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
