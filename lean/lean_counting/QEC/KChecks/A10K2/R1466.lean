import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5864 = true := by
  decide +kernel

theorem tot5864 : totK PA10K2 A10K2.t5864 = [0, 0, 465367047481, 1624313029445, 1790126139981, 711759697467, 116229101607, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5865 = true := by
  decide +kernel

theorem tot5865 : totK PA10K2 A10K2.t5865 = [0, 0, 271007797991, 1472402706845, 2158924030711, 810001911327, 46373505283, 0, 0, 0] := by
  decide +kernel

theorem rows5866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5866 = true := by
  decide +kernel

theorem tot5866 : totK PA10K2 A10K2.t5866 = [0, 0, 41350443019, 490330928607, 1734810144295, 1893406851822, 484049819371, 31768748853, 0, 0] := by
  decide +kernel

theorem rows5867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5867 = true := by
  decide +kernel

theorem tot5867 : totK PA10K2 A10K2.t5867 = [0, 0, 495852178408, 1776003497250, 1805237735535, 551240152803, 46328355238, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
